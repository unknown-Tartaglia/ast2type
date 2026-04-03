import { StyleSheet } from 'react-native';
import { CommonUtils, FONT_MUTIPLE, PlatformUtils, fontStore } from '@hw-vmall/vrn-basic-comp';

const SCALE_SIZE = FONT_MUTIPLE.FONT_LEVEL_FOUR;
export interface UserInfo {
  [propName: string]: any;
}
export default (theme, isPad, isPc, isApp, isMember, isLogin, isPadH, isWap) => {
  const textOpacity = { opacity: 0.86 };
  const appTextColor = isMember ? { ...theme.C17, ...textOpacity } : theme.C13;
  const webTextColor = isPc ? { ...theme.C11, ...textOpacity } : appTextColor;
  const maxFontSize = Math.min(CommonUtils.getScaleSize(9, SCALE_SIZE), 12);
  const appTextLineHeight = Math.min(CommonUtils.getScaleSize(16, SCALE_SIZE), 20);
  const showTextLineHeight = PlatformUtils.isIOS() ? 10 : 10.5;
  const isBigFont = fontStore.fontMutiple > FONT_MUTIPLE.FONT_LEVEL_ONE;
  const imgTop = isBigFont ? 17 : 12;
  const loginImgStyle = isLogin && !isPc && { position: 'absolute', top: imgTop, left: 12 };
  const margin = isLogin ? 64 : 16;
  const userInfoWrapMargin = isPc ? 20 : margin;
  const padHViewHeight = isBigFont ? 122 : 104;
  const viewPaddingVertical = isLogin ? 14 : 12;
  const userAvaBorderRadius = isPc ? 44 : 24;
  const userNameFontSize = isPc ? 24 : CommonUtils.getScaleSize(18, SCALE_SIZE);
  const userNameLineHeight = isPc ? 32 : CommonUtils.getScaleSize(24, SCALE_SIZE);
  const userNameMarginRight = isPc ? 11 : 3;
  const userInfoWrapPaddingVertical = isPc ? 14 : 0;
  const userInfoWrapMarginTop = isBigFont ? 5 : 0;
  const scaleTransform = PlatformUtils.isWeb() && !isPc ? [{ scale: 9 / 12 }] : [];
  const scaleHeight = isPc ? 20 : appTextLineHeight;
  const scalelineHeight = isPc ? 20 : appTextLineHeight;
  const scaleFontSize = isPc ? 12 : maxFontSize;
  const scaleWebTransform = PlatformUtils.isWeb() && !isPc ? [{ scale: 9 / 12 }] : [];
  const scaleWebHeight = isPc ? 20 : 16;
  const scaleWebLineHeight = isPc ? 20 : 16;
  const scaleWebFontSize = isPc ? 12 : 9;
  const signIconWidth = isPc ? 93 : 70;
  const signIconHeight = isPc ? 32 : 24;
  const signIconMarginTop = isPc ? 16 : 0;
  const showTextTransform = PlatformUtils.isWeb() && !isPc ? [{ scale: 8 / 12 }] : [];
  const textLineHeight = PlatformUtils.isWeb() && !isPc ? 12 : showTextLineHeight;
  const userAccountTextColor = isMember ? theme.C42 : theme.C12;
  const tagTextPaddingH = isApp ? 4 : 8;
  const appViewStyle = !isPc && { backgroundColor: 'rgba(255,255,255,1)', paddingHorizontal: 12 };
  return StyleSheet.create<UserInfo>({
    padHView: {
      height: padHViewHeight,
      justifyContent: 'center',
      backgroundColor: 'rgba(255,255,255,1)',
      borderRadius: 16,
    },
    View: {
      marginTop: 0,
      flexDirection: 'row',
      borderRadius: 16,
      paddingVertical: viewPaddingVertical,
      position: 'relative',
      ...(isPadH && isBigFont && { height: '100%' }),
      ...appViewStyle,
    },
    cricle: {
      width: 48,
      height: 48,
      position: 'relative',
      alignContent: 'center',
      alignItems: 'center',
      justifyContent: 'center',
    },
    userAva: {
      width: isPc ? 88 : 48,
      height: isPc ? 88 : 48,
      borderRadius: userAvaBorderRadius,
    },
    userName: {
      ...theme.T10,
      ...theme.C17,
      color: 'rgba(0,0,0,0.9)',
      marginRight: userNameMarginRight,
      fontSize: userNameFontSize,
      lineHeight: userNameLineHeight,
      fontWeight: '500',
    },
    userImg: {
      alignContent: 'center',
      alignItems: 'center',
      justifyContent: 'center',
      ...loginImgStyle,
    },
    userInfo: {
      flexDirection: 'row',
      marginBottom: 2,
      alignItems: 'center',
    },
    noLogin: {
      flexDirection: 'row',
    },
    userInfoWrap: {
      paddingVertical: userInfoWrapPaddingVertical,
      marginLeft: userInfoWrapMargin,
      justifyContent: 'flex-start',
      flex: 1,
      marginTop: userInfoWrapMarginTop,
    },
    userAccount: {
      ...theme.T1,
      ...theme.C42,
      maxWidth: '100%',
      fontSize: CommonUtils.getScaleSize(14, SCALE_SIZE),
      lineHeight: CommonUtils.getScaleSize(19, SCALE_SIZE),
      color: 'rgba(0,0,0,0.6)',
      fontWeight: '400',
    },
    userAccountPc: {
      ...theme.T7,
      fontSize: theme.T7.fontSize,
      lineHeight: theme.T7.lineHeight,
    },
    accountContent: {
      marginBottom: 4,
    },
    accountContentPc: {
      marginTop: 2,
    },
    tagList: {
      flexDirection: 'row',
      justifyContent: 'flex-start',
      alignItems: 'center',
    },
    tagText: {
      display: 'flex',
      flexDirection: 'row',
      alignItems: 'center',
    },
    tagTextPc: {
      height: isPc ? 20 : appTextLineHeight,
      lineHeight: isPc ? 20 : appTextLineHeight,
      textAlign: 'center',
      borderRadius: isPc ? 10 : 8,
      ...theme.S13,
      paddingHorizontal: PlatformUtils.isWeb() && !isPc ? 0 : tagTextPaddingH,
      marginRight: isPc ? 8 : 4,
    },
    txtBg: {
      height: 13,
      backgroundColor: 'rgba(249,188,100,0.2)',
      paddingRight: 3,
      paddingLeft: 7,
      borderTopRightRadius: 7.5,
      borderBottomRightRadius: 7.5,
      marginLeft: -6,
      alignItems: 'center',
      justifyContent: 'center',
      ...(isWap || PlatformUtils.isHarmony() ? { paddingTop: 1 } : {}),
    },
    tagTxt: {
      fontSize: 9,
      color: '#825B44',
      letterSpacing: 0.3,
      ...(isWap ? { lineHeight: 14 } : {}),
    },
    scale: {
      ...theme.T0,
      transform: scaleTransform,
      height: scaleHeight,
      lineHeight: scalelineHeight,
      fontSize: scaleFontSize,
      ...theme.C38,
      opacity: 0.86,
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'center',
      flexDirection: 'row',
    },
    scaleWeb: {
      ...theme.T0,
      transform: scaleWebTransform,
      height: scaleWebHeight,
      lineHeight: scaleWebLineHeight,
      fontSize: scaleWebFontSize,
      ...webTextColor,
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'center',
      flexDirection: 'row',
    },
    appText: {
      ...appTextColor,
      paddingHorizontal: 2,
      fontSize: maxFontSize,
    },
    signWrap: {
      position: 'absolute',
      right: 32,
      top: -16,
    },
    signIcon: {
      width: signIconWidth,
      height: signIconHeight,
      marginTop: signIconMarginTop,
    },
    zcInfo: {
      height: 120,
      width: 656,
      position: 'relative',
    },
    showText: {
      ...theme.T0,
      fontSize: 8,
      fontWeight: '400',
      maxWidth: 18,
      height: 10,
      transform: showTextTransform,
      color: 'black',
      justifyContent: 'center',
      alignItems: 'center',
      lineHeight: textLineHeight,
    },
    showIcon: {
      width: 10,
      height: 10,
      zIndex: 1,
      left: 1,
    },
    showAvatar: {
      height: 12,
      backgroundColor: '#FFDDA9',
      borderRadius: 6,
      bottom: -40,
      zIndex: 100,
      justifyContent: 'center',
      alignItems: 'center',
      flexDirection: 'row',
      paddingLeft: 4,
      paddingRight: 4,
      position: 'relative',
    },
    showRadius: {
      position: 'absolute',
      bottom: 4,
      width: 48,
      height: 50,
      zIndex: 99,
    },
    avaImg: {
      width: 48,
      height: 48,
      borderRadius: 24,
      zIndex: 1,
      top: -8,
      overflow: 'hidden',
    },
    medals: {
      width: 48,
      height: 20,
      display: 'flex',
      alignItems: 'flex-start',
      justifyContent: 'flex-end',
    },
    SignInContainer: {
      flexDirection: 'row',
      justifyContent: 'flex-end',
    },
    tagListContainer: {
      flexDirection: 'row',
      justifyContent: 'space-between',
      alignItems: 'center',
      ...(!isMember && { height: 16 }),
    },
    tagListContainerPc: {
      flexDirection: 'row',
      justifyContent: 'space-between',
      alignItems: 'center',
      height: 16,
      marginTop: 4,
    },
  });
};
