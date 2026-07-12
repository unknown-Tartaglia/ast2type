export interface AnimationHeaderProps {
  /**
   * 单双wap样式
   */
  _styles: any;

  /**
   * mergeStyle
   */
  mergeStyle?: any;

  /**
   * 未登录文案
   */
  unLoginText?: any;

  /**
   * newMergeStyle
   */
  newMergeStyle: any;

  /**
   * 是否登录
   */
  isLogin: boolean;

  /**
   * 会员是否展示文案
   */
  showText: boolean;

  /**
   * vpro内容
   */
  item: any;

  /**
   * mergeStyle
   */
  showIcon: boolean;

  /**
   * 头像icon
   */
  avatarIcon: string | any;

  /**
   * 左边距
   */
  marginLeft: number;

  /**
   * 用户信息动画值
   */
  userInfoAnimatedValue: any;

  /**
   * 标题动画值
   */
  titleAnimatedValue: any;

  /**
   * 用户新点击事件
   */
  userInfoClick(actionName: string | any): void;

  /**
   * 判断用户是否能点击
   */
  canClick: boolean;

  /**
   * 默认头像
   */
  defaultAvatar?: string;

  /**
   * 单框架默认登录头像
   */
  loginDefaultAvatar?: string;

  /**
   * 单框架默认未登录头像
   */
  unLoginDefaultAvatar?: string;

  /**
   * 点击登录方法
   */
  goLogin: any;

  /**
   * 用户名
   */
  userName: string;

  /**
   * 用户等级
   */
  userLevel: string;

  /**
   * 是否是会员
   */
  isMember: boolean;

  /**
   * 会员头像
   */
  avaImg: string;

  /**
   * 是否pad横屏
   */
  isPadH?: boolean;
}
